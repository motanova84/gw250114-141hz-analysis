#!/usr/bin/env python3
"""
Test script para verificar el sistema de análisis multi-evento.
"""

import os
import sys
import json


def test_script_exists():
    """Verifica que el script exista"""
    project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    script_path = os.path.join(project_root, 'multi_event_analysis_v2.py')
    assert os.path.exists(script_path), f"Script no encontrado: {script_path}"
    print("✅ Script multi_event_analysis_v2.py existe")


def test_json_file_exists():
    """Verifica que el archivo JSON de comparación exista"""
    project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    json_path = os.path.join(project_root, 'snr_h1_l1_comparison.json')
    
    assert os.path.exists(json_path), f"JSON no encontrado: {json_path}"
    print(f"✅ JSON generado: {json_path}")
    
    # Verificar tamaño mínimo (debe ser mayor a 100 bytes)
    size = os.path.getsize(json_path)
    assert size > 100, f"JSON muy pequeño: {size} bytes"
    print(f"✅ JSON tiene tamaño válido: {size} bytes")
    
    # Verificar que sea JSON válido
    with open(json_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    # Verificar estructura básica
    assert 'metadata' in data, "JSON no tiene campo 'metadata'"
    assert 'summary' in data, "JSON no tiene campo 'summary'"
    assert 'events' in data, "JSON no tiene campo 'events'"
    print("✅ JSON tiene estructura válida")
    
    # Verificar datos del resumen
    summary = data['summary']
    assert summary['total_events'] > 0, "No hay eventos analizados"
    print(f"✅ JSON contiene {summary['total_events']} eventos analizados")


def test_image_exists():
    """Verifica que la imagen exista"""
    project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    image_path = os.path.join(project_root, 'snr_h1_l1.png')
    
    if os.path.exists(image_path):
        print(f"✅ Imagen generada: {image_path}")
        # Verificar tamaño mínimo
        size = os.path.getsize(image_path)
        assert size > 50, f"Imagen muy pequeña: {size} bytes"
        print(f"✅ Imagen tiene tamaño válido: {size} bytes")
    else:
        print(f"⚠️  Imagen no encontrada en {image_path}")
        print("   Ejecutar 'python3 multi_event_analysis_v2.py' para generarla")


def test_readme_has_section():
    """Verifica que el README incluya la sección multi-evento"""
    project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    readme_path = os.path.join(project_root, 'README.md')
    
    with open(readme_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Verificar que tenga la sección
    assert '## 🔬 Resultados Multi-Evento 141.7 Hz' in content, \
        "README no incluye la sección de resultados multi-evento"
    print("✅ README incluye la sección de resultados multi-evento")
    
    # Verificar referencias a archivos
    assert 'snr_h1_l1.png' in content, "README no referencia snr_h1_l1.png"
    assert 'snr_h1_l1_comparison.json' in content, "README no referencia snr_h1_l1_comparison.json"
    assert 'multi_event_analysis_v2.py' in content, "README no referencia multi_event_analysis_v2.py"
    print("✅ README incluye todas las referencias necesarias")
    
    # Verificar que tenga tabla de eventos
    assert 'GW150914' in content and 'GW151012' in content, \
        "README no incluye tabla de eventos"
    print("✅ README incluye tabla de eventos analizados")


def test_json_data_consistency():
    """Verifica consistencia de los datos en el JSON"""
    project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    json_path = os.path.join(project_root, 'snr_h1_l1_comparison.json')
    
    with open(json_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    # Verificar frecuencia objetivo
    target_freq = data['metadata']['target_frequency']
    assert target_freq == 141.7, f"Frecuencia objetivo incorrecta: {target_freq}"
    print(f"✅ Frecuencia objetivo correcta: {target_freq} Hz")
    
    # Verificar banda de frecuencia
    freq_band = data['metadata']['frequency_band']
    assert freq_band == [140.7, 142.7], f"Banda incorrecta: {freq_band}"
    print(f"✅ Banda de frecuencia correcta: {freq_band}")
    
    # Verificar que cada evento tenga datos de detectores
    for event in data['events']:
        assert 'detectors' in event, f"Evento {event.get('event')} sin detectores"
        assert 'H1' in event['detectors'], f"Evento {event.get('event')} sin datos H1"
        assert 'L1' in event['detectors'], f"Evento {event.get('event')} sin datos L1"
    
    print("✅ Todos los eventos tienen datos de ambos detectores")


if __name__ == "__main__":
    print("🧪 Ejecutando tests de análisis multi-evento...")
    print()
    
    try:
        test_script_exists()
        test_json_file_exists()
        test_image_exists()
        test_readme_has_section()
        test_json_data_consistency()
        
        print()
        print("=" * 60)
        print("✅ Todos los tests pasaron exitosamente")
        print("=" * 60)
        sys.exit(0)
    except AssertionError as e:
        print()
        print("=" * 60)
        print(f"❌ Test falló: {e}")
        print("=" * 60)
        sys.exit(1)
    except Exception as e:
        print()
        print("=" * 60)
        print(f"❌ Error inesperado: {e}")
        print("=" * 60)
        sys.exit(1)
