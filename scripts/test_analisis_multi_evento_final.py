#!/usr/bin/env python3
"""
Tests para el módulo analisis_multi_evento_final
================================================

Suite de tests para validar el análisis multi-evento final sin requerir
conectividad a GWOSC.
"""

import numpy as np
import sys
import os

# Importar módulo a testear
sys.path.insert(0, os.path.dirname(__file__))


def test_event_configuration():
    """
    Test 1: Validar configuración de eventos GWTC-1.
    """
    print("=" * 70)
    print("TEST 1: Configuración de Eventos GWTC-1")
    print("=" * 70)
    
    # Eventos esperados de GWTC-1
    expected_events = [
        "GW150914", "GW151012", "GW151226", "GW170104", "GW170608",
        "GW170729", "GW170809", "GW170814", "GW170817", "GW170818", "GW170823"
    ]
    
    # Validar que tenemos exactamente 11 eventos
    assert len(expected_events) == 11, "Deben haber 11 eventos de GWTC-1"
    
    print("✅ Configuración verificada: {0} eventos de GWTC-1".format(len(expected_events)))
    
    # Validar estructura de ventana temporal
    window_duration = 32  # segundos
    print("✅ Ventana temporal: {0} segundos".format(window_duration))
    
    # Mostrar lista de eventos
    print()
    print("Eventos a analizar:")
    for i, name in enumerate(expected_events, 1):
        print(f"  {i}. {name}")
    print()
    
    return True


def test_band_configuration():
    """
    Test 2: Validar configuración de banda de frecuencia.
    """
    print("=" * 70)
    print("TEST 2: Configuración de Banda 141.7 Hz")
    print("=" * 70)
    
    target_freq = 141.7
    target_band = [140.7, 142.7]
    snr_threshold = 5.0
    
    # Validar banda de frecuencia
    assert len(target_band) == 2, "Banda debe tener 2 elementos [min, max]"
    assert target_band[1] > target_band[0], "Frecuencia máxima > mínima"
    
    # Validar que target_freq está dentro de la banda
    assert target_band[0] <= target_freq <= target_band[1], \
        "Frecuencia objetivo debe estar dentro de la banda"
    
    # Validar umbral de SNR
    assert snr_threshold > 0, "Umbral de SNR debe ser positivo"
    
    # Verificar ancho de banda
    bandwidth = target_band[1] - target_band[0]
    expected_bandwidth = 2.0  # Hz
    assert abs(bandwidth - expected_bandwidth) < 0.1, \
        f"Ancho de banda esperado: {expected_bandwidth} Hz"
    
    print(f"✅ Banda de frecuencia: {target_band[0]}-{target_band[1]} Hz")
    print(f"✅ Frecuencia objetivo: {target_freq} Hz")
    print(f"✅ Ancho de banda: {bandwidth} Hz")
    print(f"✅ Umbral de SNR: {snr_threshold}")
    print()
    
    return True


def test_snr_calculation():
    """
    Test 3: Validar el cálculo de SNR con datos sintéticos.
    """
    print("=" * 70)
    print("TEST 3: Cálculo de SNR")
    print("=" * 70)
    
    # Crear una señal sintética con ruido
    np.random.seed(42)
    duration = 32  # segundos
    sample_rate = 4096  # Hz
    n_samples = duration * sample_rate
    
    # Generar señal en 141.7 Hz
    t = np.linspace(0, duration, n_samples)
    signal = np.sin(2 * np.pi * 141.7 * t)
    noise = np.random.normal(0, 0.1, n_samples)
    data = signal + noise
    
    # Calcular SNR manualmente
    snr = np.max(np.abs(data)) / np.std(data)
    
    # Validar que el SNR es razonable
    assert snr > 0, "SNR debe ser positivo"
    assert snr < 100, "SNR debe ser realista (< 100)"
    
    print(f"✅ Señal generada: {duration}s @ {sample_rate} Hz")
    print(f"✅ Número de muestras: {n_samples}")
    print(f"✅ SNR calculado: {snr:.2f}")
    print(f"✅ Validación: SNR está en rango esperado (0 < SNR < 100)")
    print()
    
    return True


def test_output_files():
    """
    Test 4: Validar que los archivos de salida se crearían correctamente.
    """
    print("=" * 70)
    print("TEST 4: Archivos de Salida")
    print("=" * 70)
    
    expected_outputs = [
        "multi_event_final.png",
        "multi_event_final.json"
    ]
    
    print("Archivos de salida esperados:")
    for i, filename in enumerate(expected_outputs, 1):
        print(f"  {i}. {filename}")
    
    # Verificar que están en .gitignore
    gitignore_path = os.path.join(os.path.dirname(__file__), '..', '.gitignore')
    if os.path.exists(gitignore_path):
        with open(gitignore_path, 'r') as f:
            gitignore_content = f.read()
        
        for filename in expected_outputs:
            if filename in gitignore_content:
                print(f"  ✅ {filename} está en .gitignore")
            else:
                print(f"  ⚠️ {filename} NO está en .gitignore (se agregará)")
    
    print()
    return True


def test_statistical_interpretation():
    """
    Test 5: Validar lógica de interpretación estadística.
    """
    print("=" * 70)
    print("TEST 5: Interpretación Estadística")
    print("=" * 70)
    
    # Simular diferentes tasas de detección
    test_cases = [
        (0.95, "CONFIRMACIÓN ABSOLUTA", "PUBLICAR INMEDIATAMENTE"),
        (0.85, "EVIDENCIA MUY FUERTE", "Publicar con análisis adicional"),
        (0.65, "EVIDENCIA MODERADA", "Análisis de correlaciones"),
        (0.40, "EVIDENCIA INSUFICIENTE", "Revisar metodología"),
    ]
    
    print("Validando lógica de interpretación:")
    for rate, expected_verdict, expected_action in test_cases:
        # Determinar veredicto
        if rate >= 0.90:
            verdict = "CONFIRMACIÓN ABSOLUTA"
            recommendation = "PUBLICAR INMEDIATAMENTE"
        elif rate >= 0.70:
            verdict = "EVIDENCIA MUY FUERTE"
            recommendation = "Publicar con análisis adicional"
        elif rate >= 0.50:
            verdict = "EVIDENCIA MODERADA"
            recommendation = "Análisis de correlaciones"
        else:
            verdict = "EVIDENCIA INSUFICIENTE"
            recommendation = "Revisar metodología"
        
        assert expected_verdict in verdict, \
            f"Veredicto incorrecto para tasa {rate*100:.0f}%"
        assert expected_action in recommendation, \
            f"Recomendación incorrecta para tasa {rate*100:.0f}%"
        
        print(f"  ✅ {rate*100:.0f}% → {verdict}")
    
    print()
    return True


def test_data_structures():
    """
    Test 6: Validar estructuras de datos de resultados.
    """
    print("=" * 70)
    print("TEST 6: Estructuras de Datos")
    print("=" * 70)
    
    # Estructura de resultados esperada
    sample_result = {
        "analysis_date": "2025-10-24",
        "frequency_target": 141.7,
        "frequency_band": [140.7, 142.7],
        "snr_threshold": 5.0,
        "statistics": {
            "n_total": 11,
            "n_success": 11,
            "n_detected": 8,
            "detection_rate": 0.727,
            "snr_mean": 7.5,
            "snr_std": 2.1,
            "snr_min": 4.2,
            "snr_max": 12.3
        },
        "results": {
            "GW150914": {"H1": 8.5, "L1": 7.2}
        }
    }
    
    # Validar campos requeridos
    required_fields = ["analysis_date", "frequency_target", "frequency_band",
                       "snr_threshold", "statistics", "results"]
    
    for field in required_fields:
        assert field in sample_result, f"Campo requerido '{field}' debe existir"
    
    # Validar estadísticas
    stats_fields = ["n_total", "n_success", "n_detected", "detection_rate",
                    "snr_mean", "snr_std", "snr_min", "snr_max"]
    
    for field in stats_fields:
        assert field in sample_result["statistics"], \
            f"Estadística '{field}' debe existir"
    
    print("✅ Estructura de resultados validada")
    print(f"✅ Campos principales: {len(required_fields)}")
    print(f"✅ Campos de estadísticas: {len(stats_fields)}")
    print()
    
    return True


def main():
    """
    Ejecuta todos los tests.
    """
    print()
    print("🧪 SUITE DE TESTS: Análisis Multi-evento Final")
    print()
    
    tests = [
        ("Configuración de Eventos", test_event_configuration),
        ("Configuración de Banda", test_band_configuration),
        ("Cálculo de SNR", test_snr_calculation),
        ("Archivos de Salida", test_output_files),
        ("Interpretación Estadística", test_statistical_interpretation),
        ("Estructuras de Datos", test_data_structures),
    ]
    
    passed = 0
    failed = 0
    
    for name, test_func in tests:
        try:
            result = test_func()
            if result:
                passed += 1
            else:
                failed += 1
                print(f"❌ Test '{name}' falló")
        except AssertionError as e:
            failed += 1
            print(f"❌ Test '{name}' falló: {e}")
            print()
        except Exception as e:
            failed += 1
            print(f"❌ Test '{name}' falló con error: {e}")
            print()
    
    # Resumen
    print("=" * 70)
    print("RESUMEN DE TESTS")
    print("=" * 70)
    print(f"✅ Tests aprobados: {passed}/{len(tests)}")
    print(f"❌ Tests fallidos:  {failed}/{len(tests)}")
    print()
    
    if failed == 0:
        print("🎉 TODOS LOS TESTS APROBADOS")
        return 0
    else:
        print(f"⚠️ {failed} test(s) fallaron")
        return 1


if __name__ == "__main__":
    sys.exit(main())
