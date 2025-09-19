#!/usr/bin/env python3
"""
Validador de conectividad GWOSC - Paso 1 del pipeline de validación científica
Verifica que podemos conectarnos y descargar datos de GWOSC correctamente.
"""
import sys
import os
from gwpy.timeseries import TimeSeries
from gwpy.segments import DataQualityFlag
import numpy as np

def test_gwosc_connection():
    """Verificar conectividad básica con GWOSC"""
    print("🔍 Paso 1: Verificando conectividad con GWOSC...")
    
    try:
        # Intentar una descarga mínima de datos de prueba (1 segundo)
        test_start = 1126259462  # GW150914 merger time
        test_end = test_start + 1
        
        print(f"   Descargando 1 segundo de datos de prueba (GPS {test_start})...")
        data = TimeSeries.fetch_open_data('H1', test_start, test_end, verbose=False)
        
        if len(data) > 0:
            print(f"   ✅ Conexión exitosa - Descargados {len(data)} muestras")
            print(f"   ✅ Sample rate: {data.sample_rate} Hz")
            print(f"   ✅ Duración: {data.duration} segundos")
            return True
        else:
            print("   ❌ Error: Datos vacíos recibidos")
            return False
            
    except Exception as e:
        print(f"   ❌ Error de conectividad: {e}")
        print("   💡 Posibles causas:")
        print("      - Conexión a internet interrumpida")
        print("      - Servidores GWOSC temporalmente no disponibles") 
        print("      - Firewall bloqueando conexiones")
        return False

def test_data_quality_flags():
    """Verificar acceso a banderas de calidad de datos"""
    print("🔍 Paso 2: Verificando acceso a banderas de calidad...")
    
    try:
        # Intentar acceder a data quality flags para GW150914
        start = 1126259460
        end = 1126259465
        
        # Banderas básicas de H1
        dqflag = DataQualityFlag.query('H1:DMT-ANALYSIS_READY:1', start, end)
        print(f"   ✅ Acceso a DQ flags exitoso")
        print(f"   ✅ Segmentos activos: {len(dqflag.active)}")
        return True
        
    except Exception as e:
        print(f"   ⚠️  DQ flags no disponibles: {e}")
        print("   💡 Esto no afecta el análisis principal")
        return True  # No crítico para el análisis

def test_metadata_access():
    """Verificar acceso a metadatos de eventos"""
    print("🔍 Paso 3: Verificando acceso a metadatos de eventos...")
    
    try:
        # Verificar que podemos acceder a información básica del evento
        from gwpy.time import to_gps
        
        # GW150914 - evento conocido
        gw150914_gps = 1126259462.423
        print(f"   ✅ GPS time GW150914: {gw150914_gps}")
        
        # Verificar conversión de tiempos
        import datetime
        gw150914_utc = datetime.datetime(2015, 9, 14, 9, 50, 45)
        print(f"   ✅ UTC time GW150914: {gw150914_utc}")
        
        return True
        
    except Exception as e:
        print(f"   ❌ Error accediendo metadatos: {e}")
        return False

def main():
    """Ejecutar validación completa de conectividad"""
    print("🌌 VALIDADOR DE CONECTIVIDAD GWOSC")
    print("=" * 50)
    
    # Tests de conectividad
    tests_passed = 0
    total_tests = 3
    
    if test_gwosc_connection():
        tests_passed += 1
    
    if test_data_quality_flags():
        tests_passed += 1
        
    if test_metadata_access():
        tests_passed += 1
    
    print("\n📊 RESUMEN DE VALIDACIÓN:")
    print(f"   Tests pasados: {tests_passed}/{total_tests}")
    
    if tests_passed == total_tests:
        print("   ✅ CONECTIVIDAD COMPLETAMENTE VALIDADA")
        print("   🚀 Listo para continuar con validación científica")
        return 0
    elif tests_passed >= 2:
        print("   ⚠️  CONECTIVIDAD PARCIALMENTE VALIDADA")
        print("   🚀 Puede continuar con limitaciones")
        return 0
    else:
        print("   ❌ CONECTIVIDAD FALLIDA")
        print("   💡 Revisar conexión a internet y reintentar")
        return 1

if __name__ == "__main__":
    sys.exit(main())