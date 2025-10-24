#!/usr/bin/env python3
"""
Tests para validacion_criterios_descubrimiento.py

Pruebas unitarias para verificar que el sistema de validación
funciona correctamente y cumple con los criterios establecidos.
"""

import sys
import os
import numpy as np
import json

# Agregar el directorio actual al path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from validacion_criterios_descubrimiento import ValidadorCriteriosDescubrimiento


def test_inicializacion():
    """Test: Inicialización del validador"""
    print("Test 1: Inicialización...")
    validador = ValidadorCriteriosDescubrimiento(f0=141.7001)
    assert validador.f0 == 141.7001
    assert 'frecuencia_objetivo' in validador.resultados
    assert validador.resultados['frecuencia_objetivo'] == 141.7001
    print("   ✅ Inicialización correcta")


def test_no_artefacto_instrumental():
    """Test: Criterio 1 - No es artefacto instrumental"""
    print("Test 2: No es artefacto instrumental...")
    validador = ValidadorCriteriosDescubrimiento()
    
    # Caso: Aparece en todos los detectores
    detecciones = {
        'H1': {'freq': 141.69, 'snr': 7.47},
        'L1': {'freq': 141.75, 'snr': 0.95},
        'V1': {'freq': 141.72, 'snr': 3.21}
    }
    resultado = validador.validar_no_artefacto_instrumental(detecciones)
    assert resultado == True, "Debería pasar cuando aparece en todos los detectores"
    
    # Caso: Solo en un detector (artefacto probable)
    detecciones_mal = {
        'H1': {'freq': 141.69, 'snr': 7.47},
        'L1': {'freq': 200.00, 'snr': 0.95},
        'V1': {'freq': 180.00, 'snr': 3.21}
    }
    resultado_mal = validador.validar_no_artefacto_instrumental(detecciones_mal)
    assert resultado_mal == False, "Debería fallar cuando solo aparece en un detector"
    
    print("   ✅ Validación multi-detector funciona correctamente")


def test_no_linea_persistente():
    """Test: Criterio 2 - No es línea persistente"""
    print("Test 3: No es línea persistente...")
    validador = ValidadorCriteriosDescubrimiento()
    
    # Caso: Variación física razonable
    frecuencias = [141.69, 141.75, 141.68, 141.73, 141.70, 141.71]
    resultado = validador.validar_no_linea_persistente(frecuencias)
    assert resultado == True, "Debería pasar con variación física razonable"
    
    # Caso: Línea persistente (variación muy pequeña)
    frecuencias_persistente = [141.700, 141.701, 141.700, 141.700, 141.701]
    resultado_persistente = validador.validar_no_linea_persistente(frecuencias_persistente)
    assert resultado_persistente == False, "Debería fallar con variación muy pequeña"
    
    # Caso: Variación muy grande (no física)
    frecuencias_grandes = [100.0, 150.0, 180.0, 120.0]
    resultado_grande = validador.validar_no_linea_persistente(frecuencias_grandes)
    assert resultado_grande == False, "Debería fallar con variación muy grande"
    
    print("   ✅ Validación de variación funciona correctamente")


def test_p_value_combinado():
    """Test: Criterio 3 - No es coincidencia estadística"""
    print("Test 4: p-value combinado...")
    validador = ValidadorCriteriosDescubrimiento()
    
    # Caso: SNR altos (significancia alta)
    snr_altos = [7.47, 6.21, 8.67, 5.89, 7.23, 9.12]
    p_value = validador.calcular_p_value_combinado(snr_altos)
    assert p_value < 1e-5, f"p-value {p_value} debería ser muy pequeño con SNR altos"
    
    # Verificar que se guardaron los resultados
    assert 'no_coincidencia_estadistica' in validador.resultados['criterios']
    assert 'p_value' in validador.resultados['criterios']['no_coincidencia_estadistica']
    
    print(f"   p-value calculado: {p_value:.2e}")
    print("   ✅ Cálculo de p-value funciona correctamente")


def test_universal_gwtc1():
    """Test: Criterio 4 - Universal en GWTC-1"""
    print("Test 5: Universalidad en GWTC-1...")
    validador = ValidadorCriteriosDescubrimiento()
    
    eventos_totales = ['GW150914', 'GW151012', 'GW151226', 'GW170104', 
                       'GW170608', 'GW170729', 'GW170809', 'GW170814']
    
    # Caso: 100% de eventos
    eventos_con_senal = eventos_totales.copy()
    resultado = validador.validar_universal_gwtc1(eventos_totales, eventos_con_senal)
    assert resultado == True, "Debería pasar con 100% de eventos"
    
    # Caso: 87.5% de eventos (no cumple el umbral de 90%)
    eventos_con_senal_87 = eventos_totales[:7]  # 7 de 8 = 87.5%
    resultado_87 = validador.validar_universal_gwtc1(eventos_totales, eventos_con_senal_87)
    assert resultado_87 == False, "No debería pasar con 87.5% de eventos (< 90%)"
    
    # Caso: Menos del 80% (no cumple)
    eventos_con_senal_50 = eventos_totales[:4]  # 4 de 8 = 50%
    resultado_50 = validador.validar_universal_gwtc1(eventos_totales, eventos_con_senal_50)
    assert resultado_50 == False, "Debería fallar con menos del 90%"
    
    print("   ✅ Validación de universalidad funciona correctamente")


def test_snr_consistente():
    """Test: Criterio 5 - SNR consistente"""
    print("Test 6: SNR consistente...")
    validador = ValidadorCriteriosDescubrimiento()
    
    # Caso: SNR consistente alrededor de 21 con CV=0.30
    snr_consistente = [21.0, 18.5, 23.2, 19.8, 22.5, 20.1]
    resultado = validador.validar_snr_consistente(snr_consistente, target_snr=21, target_cv=0.30)
    assert resultado == True, "Debería pasar con SNR consistente"
    
    # Caso: SNR muy variable
    snr_variable = [5.0, 35.0, 10.0, 40.0, 8.0]
    resultado_variable = validador.validar_snr_consistente(snr_variable, target_snr=21, target_cv=0.30)
    assert resultado_variable == False, "Debería fallar con SNR muy variable"
    
    print("   ✅ Validación de SNR consistente funciona correctamente")


def test_todos_significativos():
    """Test: Criterio 6 - Todos significativos (>10σ)"""
    print("Test 7: Todos significativos...")
    validador = ValidadorCriteriosDescubrimiento()
    
    # Caso: Todos por encima de 10σ
    snr_altos = [12.3, 15.7, 11.2, 13.8, 14.5, 10.9]
    resultado = validador.validar_todos_significativos(snr_altos, umbral_sigma=10)
    assert resultado == True, "Debería pasar cuando todos > 10σ"
    
    # Caso: Algunos por debajo de 10σ
    snr_mixtos = [12.3, 5.7, 11.2, 3.8, 14.5, 10.9]
    resultado_mixto = validador.validar_todos_significativos(snr_mixtos, umbral_sigma=10)
    assert resultado_mixto == False, "Debería fallar cuando algunos < 10σ"
    
    print("   ✅ Validación de significancia funciona correctamente")


def test_estandares_descubrimiento():
    """Test: Criterio 7 - Estándares de descubrimiento"""
    print("Test 8: Estándares de descubrimiento...")
    validador = ValidadorCriteriosDescubrimiento()
    
    # Caso: Cumple ambos estándares (5σ y 3σ)
    snr_altos = [7.47, 6.21, 8.67, 5.89, 7.23]
    estandares = validador.validar_estandares_descubrimiento(snr_altos)
    assert estandares['particulas'] == True, "Debería cumplir estándar de partículas (5σ)"
    assert estandares['astronomia'] == True, "Debería cumplir estándar de astronomía (3σ)"
    
    # Caso: Solo cumple astronomía
    snr_medios = [4.2, 3.8, 4.5, 3.5]
    estandares_medios = validador.validar_estandares_descubrimiento(snr_medios)
    assert estandares_medios['particulas'] == False, "No debería cumplir estándar de partículas"
    assert estandares_medios['astronomia'] == True, "Debería cumplir estándar de astronomía"
    
    print("   ✅ Validación de estándares funciona correctamente")


def test_generacion_informe():
    """Test: Generación de informe completo"""
    print("Test 9: Generación de informe...")
    validador = ValidadorCriteriosDescubrimiento()
    
    # Ejecutar algunas validaciones
    detecciones = {'H1': {'freq': 141.69, 'snr': 7.47}, 'L1': {'freq': 141.75, 'snr': 0.95}}
    validador.validar_no_artefacto_instrumental(detecciones)
    
    frecuencias = [141.69, 141.75, 141.68, 141.73]
    validador.validar_no_linea_persistente(frecuencias)
    
    # Generar informe
    output_file = '/tmp/test_informe_validacion.json'
    resultados = validador.generar_informe_completo(output_file)
    
    # Verificar que se creó el archivo
    assert os.path.exists(output_file), "Archivo de informe debería existir"
    
    # Verificar estructura del informe
    assert 'resumen' in resultados
    assert 'criterios_cumplidos' in resultados['resumen']
    assert 'validacion_exitosa' in resultados['resumen']
    
    # Leer y verificar JSON
    with open(output_file, 'r') as f:
        data = json.load(f)
        assert 'frecuencia_objetivo' in data
        assert data['frecuencia_objetivo'] == 141.7001
    
    print("   ✅ Generación de informe funciona correctamente")


def test_integracion_completa():
    """Test: Integración completa del sistema"""
    print("Test 10: Integración completa...")
    validador = ValidadorCriteriosDescubrimiento()
    
    # Simular validación completa
    detecciones = {
        'H1': {'freq': 141.69, 'snr': 7.47},
        'L1': {'freq': 141.75, 'snr': 0.95},
        'V1': {'freq': 141.72, 'snr': 3.21}
    }
    validador.validar_no_artefacto_instrumental(detecciones)
    
    frecuencias = [141.69, 141.75, 141.68, 141.73, 141.70]
    validador.validar_no_linea_persistente(frecuencias)
    
    snr = [7.47, 6.21, 5.67, 4.89, 6.23]
    validador.calcular_p_value_combinado(snr)
    
    eventos_total = ['GW150914', 'GW151012', 'GW151226', 'GW170104']
    eventos_senal = ['GW150914', 'GW151012', 'GW151226', 'GW170104']
    validador.validar_universal_gwtc1(eventos_total, eventos_senal)
    
    validador.validar_snr_consistente(snr, target_snr=21, target_cv=0.30)
    
    snr_altos = [12.3, 15.7, 11.2, 13.8]
    validador.validar_todos_significativos(snr_altos, umbral_sigma=10)
    
    validador.validar_estandares_descubrimiento(snr_altos)
    
    # Generar informe final
    output_file = '/tmp/test_informe_completo.json'
    resultados = validador.generar_informe_completo(output_file)
    
    # Verificar que hay resultados para todos los criterios
    assert len(resultados['criterios']) >= 7, "Debería haber al menos 7 criterios validados"
    
    print(f"   Criterios validados: {len(resultados['criterios'])}")
    print(f"   Criterios cumplidos: {resultados['resumen']['criterios_cumplidos']}")
    print("   ✅ Integración completa funciona correctamente")


def run_all_tests():
    """Ejecutar todos los tests"""
    print("=" * 70)
    print("TESTS DE VALIDACIÓN DE CRITERIOS DE DESCUBRIMIENTO")
    print("=" * 70)
    print()
    
    tests = [
        test_inicializacion,
        test_no_artefacto_instrumental,
        test_no_linea_persistente,
        test_p_value_combinado,
        test_universal_gwtc1,
        test_snr_consistente,
        test_todos_significativos,
        test_estandares_descubrimiento,
        test_generacion_informe,
        test_integracion_completa
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"   ❌ FALLÓ: {str(e)}")
            failed += 1
        except Exception as e:
            print(f"   ❌ ERROR: {str(e)}")
            failed += 1
        print()
    
    print("=" * 70)
    print(f"RESULTADOS: {passed} tests pasados, {failed} tests fallidos")
    print("=" * 70)
    
    return failed == 0


if __name__ == '__main__':
    success = run_all_tests()
    sys.exit(0 if success else 1)
